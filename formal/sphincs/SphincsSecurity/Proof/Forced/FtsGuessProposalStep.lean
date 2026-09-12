import SphincsSecurity.Proof.Forced.FtsGuessMonitoredPayment
import SphincsSecurity.Proof.Residual.RetainedResidualProposalSupport
import SphincsSecurity.Proof.Residual.RetainedResidualProposalWord
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult signingAnnotation completeRecordIndex attachRejectedWord
  digestCompletionValue pmfLift_bind pmfLift_map)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete signDigestLoop

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem bind_const_of_eq {A B : Type} (law : SPMF A) (next : A → SPMF B) (after : SPMF B) (hnext : ∀ value, next value = after)
    (hconst : (law >>= fun _ => after) = after) : (law >>= next) = after := by
  rw [show next = fun _ => after from funext hnext]
  exact hconst

/-! ### The forced signing law and its digest record -/

theorem publicSigningWork_bank_digest' (key : SecretKey) (hparameter : key.parameter = parameter) (hroot : key.root = root)
    (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (actual : CanonicalProbeRouting.Labels) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1).1, result.2)) <$>
      𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root known words selections message)).run cache] =
        digestCompletionValue known words selections actual <$>
          𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] := by
  subst hparameter hroot
  exact publicSigningWork_bank_digest key known words selections actual message cache

noncomputable def forcedSigning (message : Message) (state : MonitoredState) :
    SPMF (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) :=
  cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) state.1

def forcedSigningView (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) : Option FewTimeView :=
  result.1.1.2

theorem forcedSigning_digestRecord (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hresult : forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0) :
    ∃ loop, loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit (monitorKey parameter root) message)).run state.1.1) ∧
      result.2.1 = loop.2 ∧ DigestCompletionPreservesMessages (monitorKey parameter root) loop (result.1.1, result.2.1) := by
  rw [forcedSigning, cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1
    hvalid hinputs (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy),
    RetainedObservation.bind_nonzero] at hresult
  obtain ⟨secrets, _, hresult⟩ := hresult
  obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
  have h := map_nonzero_of _ (fun result => ((completePublicSigningRecord
    (fun index tree leaf => secretLabels secrets (.ftsStart index tree leaf)) result.1).1, result.2)) raw hraw
  rw [publicSigningWork_bank_digest' parameter root (monitorKey parameter root) rfl rfl (known otsSecret labels)
    (referenceFamilyWords selections dummy) selections (secretLabels secrets) message state.1.1] at h
  obtain ⟨loop, hloop, heq⟩ := map_nonzero_source' _ _ _ h
  refine ⟨loop, (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hloop, ?_, ?_⟩
  · exact congrArg Prod.snd heq
  · have hvalue : ((completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) raw.1).1, raw.2) =
        digestCompletionValue (known otsSecret labels) (referenceFamilyWords selections dummy) selections (secretLabels secrets) loop := heq
    rw [hvalue]
    exact RetainedResidual.digestCompletionValue_preservesMessages (monitorKey parameter root) _ _ _ _ loop

theorem forcedSigning_selectedView (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    forcedSigningView <$> forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state =
      selectedLoopView? <$>
        𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit (monitorKey parameter root) message)).run (monitorView state).1] := by
  rw [forcedSigning, cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1
    hvalid hinputs (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy), map_bind]
  simp only [Functor.map_map]
  calc
    _ = complete state.1.2.allowed >>= fun _ => selectedLoopView? <$>
        𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit (monitorKey parameter root) message)).run state.1.1] := by
      apply congrArg (complete state.1.2.allowed >>= ·)
      funext secrets
      have h := congrArg (Functor.map (fun value : (Option Signature × Option FewTimeView) × QueryCache HashSpec => value.1.2))
        (publicSigningWork_bank_digest' parameter root (monitorKey parameter root) rfl rfl (known otsSecret labels)
          (referenceFamilyWords selections dummy) selections (secretLabels secrets) message state.1.1)
      simp only [Functor.map_map] at h
      rw [show (fun result : (PublicSigningRecord × QueryCache HashSpec) =>
          forcedSigningView (completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) result.1,
            (result.2, FtsGuessSigning.completedState
              (SecretGuessObservation.environment (referenceAnswers parameter root otsSecret labels inputs hencoding
                ⟨selections, rows, fun _ => 0⟩ dummy)) secrets result.1 state.1.2))) =
          fun result => ((completePublicSigningRecord (fun index tree leaf => secretLabels secrets (.ftsStart index tree leaf)) result.1).1,
            result.2).1.2 from rfl, h]
      congr 1
      funext loop
      exact (RetainedResidual.digestCompletionValue_preservesMessages (monitorKey parameter root) _ _ _ _ loop).1.1
    _ = _ := by
      rw [complete_of_nonempty _ hvalid, RetainedObservation.lift_bind_const, monitorView_fst]

/-! ### Completing the proposal index -/

noncomputable def completedForcedSigning (message : Message) (state : MonitoredState) :
    SPMF ((((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) × Index) :=
  completeRecordIndex (forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state) forcedSigningView

theorem completedForcedSigning_record (message : Message) (state : MonitoredState) :
    Prod.fst <$> completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state =
      forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state :=
  RetainedResidual.completeRecordIndex_record _ _

theorem completedForcedSigning_index (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    Prod.snd <$> completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state =
      (liftM ((originalProposalRecord (monitorKey parameter root) (.inr message) (monitorView state).1).map (fun record => record.index)) :
        SPMF Index) := by
  rw [completedForcedSigning, RetainedResidual.completeRecordIndex_index,
    forcedSigning_selectedView parameter root otsSecret labels inputs hencoding selections rows dummy slot message state hvalid hinputs,
    RetainedResidual.originalProposalRecord_index_loop]

/-! ### Proposal steps -/

noncomputable def signResult (message : Message) (annotation : Nat × Index) (state : MonitoredState)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) :
    AdversaryStep (.inr message) × MonitoredState :=
  (((result.1.1.1, result.1.2), 1),
    (result.2, certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter (.inr message) (monitorView state) annotation.1
      (proposalOfSigningRecord message result.1 result.2.1 (result.1.1.2.elim annotation.2 Prod.fst))))

theorem monitoredSignStep_eq (message : Message) (state : MonitoredState) :
    monitoredSignStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter message state =
      ((liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _) >>= fun annotation =>
        signResult parameter root budget required stopAfter message annotation state <$>
          forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state) := rfl

theorem signResult_completed (message : Message) (length : Nat) (fallback : Index) (state : MonitoredState)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) :
    signResult parameter root budget required stopAfter message (length, (forcedSigningView result).elim fallback Prod.fst) state result =
      signResult parameter root budget required stopAfter message (length, fallback) state result := by
  rcases result with ⟨⟨⟨signature, view⟩, trace⟩, cached⟩
  cases view <;> rfl

theorem completedForcedSigning_monitored (message : Message) (length : Nat) (state : MonitoredState) :
    (fun result => signResult parameter root budget required stopAfter message (length, result.2) state result.1) <$>
        completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state =
      ((liftM (PMF.uniformOfFintype Index) : SPMF Index) >>= fun fallback =>
        signResult parameter root budget required stopAfter message (length, fallback) state <$>
          forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state) := by
  rw [completedForcedSigning, RetainedResidual.completeRecordIndex_fallback, map_bind]
  simp only [Functor.map_map, signResult_completed]

abbrev ProposalState := List Index × MonitoredState

noncomputable def proposalStep : (input : (OracleWorld + SigningSpec).Domain) → ProposalState → SPMF (AdversaryStep input × ProposalState)
  | .inl input, state =>
      (fun result => (result.1, (state.1, result.2))) <$>
        monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input) state.2
  | .inr message, state =>
      if CertificateMonitorActive (monitorKey parameter root) budget (.inr message) (monitorView state.2) then
        (fun result =>
          let after := signResult parameter root budget required stopAfter message (result.1.length + 1, result.2.2) state.2 result.2.1
          (after.1, (state.1 ++ (result.1 ++ [result.2.2]), after.2))) <$>
          attachRejectedWord (completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.2)
            (originalRejectedProposal (monitorKey parameter root) (fun current => current.2.spent) (.inr message) (monitorView state.2))
      else
        (fun result => (result.1, (state.1, result.2))) <$>
          monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inr message) state.2

theorem proposalStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) :
    Prod.map id Prod.snd <$> proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state =
      monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.2 := by
  cases input with
  | inl input =>
      rw [proposalStep, Functor.map_map]
      exact id_map' _
  | inr message =>
      rw [proposalStep]
      split_ifs with hactive
      · rw [Functor.map_map]
        calc
          _ = (fun result => signResult parameter root budget required stopAfter message (result.1, result.2.2) state.2 result.2.1) <$>
              ((fun result => (result.1.length + 1, result.2)) <$>
                attachRejectedWord
                  (completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.2)
                  (originalRejectedProposal (monitorKey parameter root) (fun current => current.2.spent) (.inr message) (monitorView state.2))) := by
            rw [Functor.map_map]
            rfl
          _ = _ := by
            rw [RetainedResidual.attachRejectedWord_length, map_bind, monitoredStep, monitoredSignStep_eq, signingAnnotation, if_pos hactive,
              pmfLift_bind]
            simp only [Functor.map_map, pmfLift_map, bind_assoc, bind_map_left]
            simp_rw [completedForcedSigning_monitored]
      · rw [Functor.map_map]
        exact id_map' _

theorem proposalStep_forced (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState)
    (result : AdversaryStep input × ProposalState)
    (hresult : proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.2
      (result.1, result.2.2) ≠ 0 := by
  have h := map_nonzero_of _ (Prod.map id Prod.snd) result hresult
  rwa [proposalStep_erasure] at h

theorem proposalStep_valid (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (result : AdversaryStep input × ProposalState)
    (hresult : proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) : Valid result.2.2 :=
  monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state.2 hvalid
    _ (proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      result hresult)

theorem proposalStep_complete (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (hinputs : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (total : Nat) :
    (proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
      fun result => (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1) : SPMF (List Index)) := by
  cases input with
  | inl input =>
      rw [proposalStep, bind_map_left]
      exact bind_const_of_eq _ _ _ (fun _ => rfl)
        (monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (.inl input) state.2 hvalid _)
  | inr message =>
      rw [proposalStep]
      split_ifs with hactive
      · rw [bind_map_left]
        have hbound : ProposalCacheBound (monitorKey parameter root) (monitorView state.2).1 (monitorView state.2).2.spent := hactive.2.1.2.1
        rw [originalRejectedProposal, dif_pos hbound]
        exact RetainedResidual.attachRejectedWord_complete _ Prod.snd
          (originalProposalRecord (monitorKey parameter root) (.inr message) (monitorView state.2).1) (fun record => record.index)
          (completedForcedSigning_index parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.2 hvalid
            (hinputs message rfl))
          (originalProposalRecord_cap (monitorKey parameter root) message (monitorView state.2).1 (monitorView state.2).2.spent hbound) total state.1
      · rw [bind_map_left]
        exact bind_const_of_eq _ _ _ (fun _ => rfl)
          (monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (.inr message) state.2 hvalid _)

theorem expected_proposalStep_terminalPotential (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (hinputs : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (total : Nat) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : SPMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (proposalStep_complete parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      hvalid hinputs total)
  rw [tsum_probOutput_bind_mul] at h
  simpa only [terminalProposalPotential, SPMF.probOutput_liftM] using h

/-! ### Proposal runs -/

noncomputable def proposalRun {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    ProposalState → SPMF ((((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × ProposalState) :=
  OracleComp.construct (fun value state => pure ((((value, []), 1), 1), state))
    (fun input _ next state =>
      proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$> next step.1.1.1 step.2) computation

theorem proposalRun_pure {Result : Type} (value : Result) (state : ProposalState) :
    proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (pure value) state =
      pure ((((value, []), 1), 1), state) := rfl

theorem proposalRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) (state : ProposalState) :
    proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      (proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>= fun step =>
        (fun tail => (combineStep input step.1 tail.1, tail.2)) <$>
          proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next step.1.1.1) step.2) := by
  rw [proposalRun, OracleComp.construct_query_bind]
  rfl

theorem proposalRun_erasure {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ProposalState) :
    Prod.map id Prod.snd <$>
        proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state =
      monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state.2 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [proposalRun_pure, monitoredRun_pure, map_pure]; rfl
  | query_bind input next ih =>
      rw [proposalRun_query_bind, map_bind, monitoredRun_query_bind,
        ← proposalStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state,
        bind_map_left]
      apply congrArg (_ >>= ·)
      funext step
      simp only [Prod.map_fst, Prod.map_snd, id_eq]
      rw [Functor.map_map, ← ih step.1.1.1 step.2, Functor.map_map]
      rfl

theorem proposalRun_forced {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : ProposalState)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × ProposalState)
    (hresult : proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state.2
      (result.1, result.2.2) ≠ 0 := by
  have h := map_nonzero_of _ (Prod.map id Prod.snd) result hresult
  rwa [proposalRun_erasure] at h

/-! ### Coverage along proposal runs -/

theorem covered_step_digest (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query input) >>= next) state) :
    ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs := by
  intro message heq
  subst heq
  exact covered_sign_digest parameter root otsSecret inputs message next state hvalid hcovered

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

include hauxiliary in
theorem proposalRun_complete (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state.2) (total : Nat) :
    (proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state >>=
      fun result => (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1) : SPMF (List Index)) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [proposalRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [proposalRun_query_bind, bind_assoc]
      calc
        _ = proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
            fun result => (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index)) := by
          apply RetainedObservation.bind_congr
          intro result hresult
          rw [bind_map_left]
          have hforced := proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter input state result hresult
          exact ih result.1.1.1 result.2
            (proposalStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
              state hvalid result hresult)
            (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
              input next state.2 hvalid hcovered (result.1, result.2.2) hforced)
        _ = _ := proposalStep_complete parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state hvalid (covered_step_digest parameter root otsSecret inputs input next state.2 hvalid hcovered) total

/-! ### The completed proposal run -/

theorem monitoredWorldRun_bind_const {Result Other : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState)
    (hvalid : Valid state) (after : SPMF Other) :
    (monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter computation state >>=
      fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [monitoredWorldRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [monitoredWorldRun_query_bind, bind_assoc]
      rw [RetainedObservation.bind_congr _ _ (fun _ => after) (fun step hstep => by
        rw [bind_map_left]
        exact ih step.1.1.1 step.2 (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter (.inl input) state hvalid step hstep))]
      exact monitoredWorldStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state hvalid after

noncomputable def proposalCompletedRun (adversary : Adversary) (state : ProposalState) : SPMF (Completed × ProposalState) :=
  proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (adversary.main ⟨root, parameter⟩) state >>= fun before =>
    (fun checked => ((before.1, checked.1), (before.2.1, checked.2))) <$>
      monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (verifyComputation parameter root before.1.1.1.1) before.2.2

theorem proposalCompletedRun_erasure (adversary : Adversary) (state : ProposalState) :
    Prod.map id Prod.snd <$>
        proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary state =
      monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary
        state.2 := by
  rw [proposalCompletedRun, monitoredCompletedRun_eq, map_bind, ← proposalRun_erasure, bind_map_left]
  apply congrArg (_ >>= ·)
  funext before
  rw [Functor.map_map]
  rfl

include hauxiliary in
theorem proposalCompletedRun_complete (adversary : Adversary) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.2) (total : Nat) :
    (proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary state >>=
      fun result => (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1) : SPMF (List Index)) := by
  rw [proposalCompletedRun, bind_assoc]
  calc
    _ = proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state >>= fun before =>
          (liftM (completeProposalWord (PMF.uniformOfFintype Index) total before.2.1) : SPMF (List Index)) := by
      apply RetainedObservation.bind_congr
      intro before hbefore
      rw [bind_map_left]
      have hforced := proposalRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state before hbefore
      exact bind_const_of_eq _ _ _ (fun _ => rfl)
        (monitoredWorldRun_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          _ before.2.2 (monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (adversary.main ⟨root, parameter⟩) state.2 hvalid _ hforced) _)
    _ = _ := proposalRun_complete parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
      (adversary.main ⟨root, parameter⟩) state hvalid hcovered total

include hauxiliary in
theorem expected_proposalCompletedRun_terminalPotential (adversary : Adversary) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.2) (total : Nat)
    (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : SPMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (proposalCompletedRun_complete parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      hauxiliary adversary state hvalid hcovered total)
  rw [tsum_probOutput_bind_mul] at h
  simpa only [terminalProposalPotential, SPMF.probOutput_liftM] using h

end SphincsSecurity.Concrete.FtsGuessHash
