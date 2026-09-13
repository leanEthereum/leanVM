import SphincsSecurity.Proof.Forced.FtsGuessProposalStep
import SphincsSecurity.Proof.Residual.RetainedResidualProposalInvariant
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult signingAnnotation completeRecordIndex attachRejectedWord proposalStop
  proposalStop_eq)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete signDigestLoop

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

/-! ### World steps keep the observed signing views -/

theorem worldStep_cache_le (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (result : OracleWorld.Range input × CachedState)
    (hresult : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input)
      state.1 result ≠ 0) :
    state.1.1 ≤ result.2.1 ∧ (messageAnswers parameter result.2.1 = messageAnswers parameter state.1.1 ∨
      ∃ hash, input = .inr hash ∧ MessageHashInput parameter hash) := by
  cases input with
  | inl sample =>
      rw [cachedForcedRun_world_unif'] at hresult
      obtain ⟨answer, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ⟨le_rfl, Or.inl rfl⟩
  | inr hash =>
      have hsupport := cachedForcedRun_world_hash_support' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash
        state.1 result hresult
      refine ⟨hsupport.2.1, ?_⟩
      by_cases hmessage : MessageHashInput parameter hash
      · exact Or.inr ⟨hash, rfl, hmessage⟩
      · exact Or.inl (messageAnswers_eq_of_cache_of_ne parameter state.1.1 result.2.1 hash hmessage hsupport.1)

theorem worldStep_observedViews (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached parameter state.1.1 root log) (result : OracleWorld.Range input × CachedState)
    (hresult : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input)
      state.1 result ≠ 0) :
    observedOptionalSigningViews (messageAnswers parameter result.2.1) root log =
      observedOptionalSigningViews (messageAnswers parameter state.1.1) root log := by
  obtain ⟨hle, _⟩ := worldStep_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot input state hinputs result hresult
  exact observedOptionalSigningViews_cache_stable parameter root _ _ log hle hsigned

theorem worldStep_digestsCached (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached parameter state.1.1 root log) (result : OracleWorld.Range input × CachedState)
    (hresult : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input)
      state.1 result ≠ 0) :
    SigningDigestsCached parameter result.2.1 root log :=
  hsigned.mono (worldStep_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot input state hinputs result hresult).1

/-! ### Signing steps add one observed view at the proposed index -/

theorem forcedSigning_cache_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hresult : forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0) :
    state.1.1 ≤ result.2.1 := by
  obtain ⟨loop, hloop, hcache, _⟩ := forcedSigning_digestRecord parameter root otsSecret labels inputs hencoding selections rows dummy slot
    message state hvalid hinputs result hresult
  rw [hcache]
  exact simulateQ_romImpl_cache_le _ _ _ hloop

theorem forcedSigning_digestsCached (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached parameter state.1.1 root log)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hresult : forcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0) :
    SigningDigestsCached parameter result.2.1 root (log ++ [⟨message, result.1.1.1⟩]) := by
  obtain ⟨loop, hloop, hcache, hcompletion⟩ := forcedSigning_digestRecord parameter root otsSecret labels inputs hencoding selections rows dummy
    slot message state hvalid hinputs result hresult
  have hle : state.1.1 ≤ result.2.1 := by
    rw [hcache]
    exact simulateQ_romImpl_cache_le _ _ _ hloop
  intro entry hentry signature hsignature
  rcases List.mem_append.mp hentry with hold | hnew
  · exact (hsigned.mono hle) entry hold signature hsignature
  · obtain rfl := List.mem_singleton.mp hnew
    obtain ⟨output, houtput, _, _⟩ := digestCompletion_successful_cached_output (monitorKey parameter root) message state.1.1 loop hloop
      (result.1.1, result.2.1) hcompletion signature hsignature
    exact Option.ne_none_iff_exists'.mpr ⟨output, houtput⟩

theorem completedForcedSigning_observed_index (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (result : (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) × Index)
    (hresult : completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0)
    (view : FewTimeView)
    (hview : observedSigningView? (messageAnswers parameter result.1.2.1) root ⟨message, result.1.1.1.1⟩ = some view) :
    result.2 = view.1 := by
  have hraw := map_nonzero_of _ Prod.fst result hresult
  rw [completedForcedSigning_record] at hraw
  obtain ⟨loop, hloop, _, hcompletion⟩ := forcedSigning_digestRecord parameter root otsSecret labels inputs hencoding selections rows dummy slot
    message state hvalid hinputs result.1 hraw
  cases hs : result.1.1.1.1 with
  | none => simp [observedSigningView?, hs] at hview
  | some signature =>
      obtain ⟨output, houtput, _, hselected⟩ := digestCompletion_successful_cached_output (monitorKey parameter root) message state.1.1 loop
        hloop (result.1.1.1, result.1.2.1) hcompletion signature hs
      dsimp only at houtput hselected
      have houtput' : result.1.2.1 (tweakableHashInput parameter .message (messageDigestPayload root message signature.randomness)) =
          some output := houtput
      have hv : hashOutputFewTimeView output = view := by
        simpa [observedSigningView?, hs, messageAnswers, houtput'] using hview
      have hselected' : forcedSigningView result.1 = some (hashOutputFewTimeView output) := hselected
      exact (RetainedResidual.completeRecordIndex_selected _ forcedSigningView result hresult _ hselected').trans (congrArg Prod.fst hv)

theorem completedForcedSigning_slots_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached parameter state.1.1 root log)
    (result : (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) × Index)
    (hresult : completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state result ≠ 0)
    (index : Index) :
    (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers parameter result.1.2.1) root
      (log ++ [⟨message, result.1.1.1.1⟩])) index).card ≤
        (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers parameter state.1.1) root log) index).card +
          if result.2 = index then 1 else 0 := by
  have hraw := map_nonzero_of _ Prod.fst result hresult
  rw [completedForcedSigning_record] at hraw
  have hle := forcedSigning_cache_le parameter root otsSecret labels inputs hencoding selections rows dummy slot message state hvalid hinputs
    result.1 hraw
  have hstable := observedOptionalSigningViews_cache_stable parameter root _ _ log hle hsigned
  unfold observedOptionalSigningViews
  rw [signingSlotsAtIndex_log_append_card]
  have heq := congrArg (fun views => (signingSlotsAtIndex views index).card) hstable
  apply Nat.add_le_add heq.le
  split_ifs with hobserved hindex hindex
  · exact le_rfl
  · obtain ⟨view, hview, hsource⟩ := hobserved
    exact False.elim (hindex ((completedForcedSigning_observed_index parameter root otsSecret labels inputs hencoding selections rows dummy
      slot message state hvalid hinputs result hresult view hview).trans hsource))
  · exact Nat.zero_le _
  · exact le_rfl

/-! ### The proposal invariant -/

def ProposalInvariant (total : Nat) (state : ProposalState) : Prop :=
  CertificateProposalInvariant (monitorKey parameter root) total (state.1, monitorView state.2)

theorem worldStep_proposalInvariant (total : Nat) (input : OracleWorld.Domain) (state : ProposalState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (hinv : ProposalInvariant parameter root total state)
    (result : OracleWorld.Range input × CachedState)
    (hresult : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (worldProgram parameter labels input)
      state.2.1 result ≠ 0) :
    ProposalInvariant parameter root total (state.1,
      (result.2, certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop stopAfter) (.inl input)
        (monitorView state.2) 0 (proposalOfWorldResult parameter input (result.1, result.2.1)))) := by
  by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget (.inl input) (monitorView state.2)
  · have hbefore := hinv hactive.1
    have hstable := worldStep_observedViews parameter root otsSecret labels inputs hencoding selections rows dummy slot input state.2 hinputs
      state.2.2.log hactive.2.1.1 result hresult
    have hafter := certificateProposalInvariant_advance (monitorKey parameter root) budget total required stopAfter (.inl input)
      (state.1, monitorView state.2) [] 0 (proposalOfWorldResult parameter input (result.1, result.2.1)) hinv hactive rfl
      (fun index => by
        change (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers parameter result.2.1) root (state.2.2.log ++ [])) index).card ≤
          (state.1 ++ []).count index
        rw [List.append_nil, List.append_nil, hstable]
        exact hbefore.counts_le index)
    rw [← proposalStop_eq] at hafter
    simpa only [ProposalInvariant, originalProposalAdvance, monitorView, proposalOfWorldResult, List.append_nil] using hafter
  · intro hpost
    change (certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop stopAfter) (.inl input) (monitorView state.2) 0
      (proposalOfWorldResult parameter input (result.1, result.2.1))).stopped = false at hpost
    simp only [certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost

theorem signStep_proposalInvariant (total : Nat) (message : Message) (state : ProposalState) (hvalid : Valid state.2)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hinv : ProposalInvariant parameter root total state)
    (hactive : CertificateMonitorActive (monitorKey parameter root) budget (.inr message) (monitorView state.2))
    (word : List Index) (result : (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState) × Index)
    (hresult : completedForcedSigning parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.2 result ≠ 0) :
    ProposalInvariant parameter root total (state.1 ++ (word ++ [result.2]),
      (signResult parameter root budget required (proposalStop stopAfter) message (word.length + 1, result.2) state.2 result.1).2) := by
  have heffective : result.1.1.1.2.elim result.2 Prod.fst = result.2 :=
    RetainedResidual.completeRecordIndex_effective _ forcedSigningView result hresult
  have hbefore := hinv hactive.1
  have hafter := certificateProposalInvariant_advance (monitorKey parameter root) budget total required stopAfter (.inr message)
    (state.1, monitorView state.2) (word ++ [result.2]) (word.length + 1)
    (proposalOfSigningRecord message result.1.1 result.1.2.1 result.2) hinv hactive
    (by simp only [List.length_append, List.length_singleton]) (fun index => by
      have hc := completedForcedSigning_slots_le parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.2
        hvalid hinputs state.2.2.log hactive.2.1.1 result hresult index
      calc
        _ ≤ _ := hc
        _ ≤ state.1.count index + if result.2 = index then 1 else 0 := Nat.add_le_add_right (hbefore.counts_le index) _
        _ ≤ (state.1 ++ (word ++ [result.2])).count index := by
          simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
          split_ifs <;> omega)
  rw [← proposalStop_eq] at hafter
  simpa only [ProposalInvariant, signResult, heffective, originalProposalAdvance, monitorView, proposalOfSigningRecord] using hafter

theorem proposalStep_invariant (total : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (hworld : ∀ world, input = .inl world → hashInputs (liftM (OracleWorld.query world)) ⊆ inputs)
    (hsign : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (hinv : ProposalInvariant parameter root total state) (result : AdversaryStep input × ProposalState)
    (hresult : proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
      input state result ≠ 0) :
    ProposalInvariant parameter root total result.2 := by
  cases input with
  | inl input =>
      rw [proposalStep] at hresult
      obtain ⟨middle, hmiddle, rfl⟩ := map_nonzero_source' _ _ _ hresult
      rw [monitoredStep, monitoredWorldStep] at hmiddle
      obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hmiddle
      exact worldStep_proposalInvariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        total input state (hworld input rfl) hinv raw hraw
  | inr message =>
      rw [proposalStep] at hresult
      split_ifs at hresult with hactive
      · obtain ⟨source, hsource, rfl⟩ := map_nonzero_source' _ _ _ hresult
        have hrecord := map_nonzero_of _ Prod.snd source hsource
        rw [RetainedResidual.attachRejectedWord_record] at hrecord
        exact signStep_proposalInvariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          total message state hvalid (hsign message rfl) hinv hactive source.1 source.2 hrecord
      · obtain ⟨middle, hmiddle, rfl⟩ := map_nonzero_source' _ _ _ hresult
        rw [monitoredStep, monitoredSignStep, RetainedObservation.bind_nonzero] at hmiddle
        obtain ⟨annotation, _, hmiddle⟩ := hmiddle
        obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hmiddle
        intro hpost
        change (certificateMonitorUpdate (monitorKey parameter root) budget required (proposalStop stopAfter) (.inr message)
          (monitorView state.2) annotation.1
          (proposalOfSigningRecord message raw.1 raw.2.1 (raw.1.1.2.elim annotation.2 Prod.fst))).stopped = false at hpost
        simp only [certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost

end SphincsSecurity.Concrete.FtsGuessHash
