import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualProposalIndex
import SphincsSecurity.Proof.Residual.RetainedResidualWorldKernel
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  lazyRun environment signDigestLoop ResidualByteFrontend.jointSigningProgram
set_option backward.isDefEq.respectTransparency false

theorem map_nonzero_source {A B : Type} (law : SPMF A) (f : A → B) (result : B)
    (hresult : (f <$> law) result ≠ 0) : ∃ source, law source ≠ 0 ∧ result = f source := by
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨source, hsource, hresult⟩ := hresult
  exact ⟨source, hsource, by simpa only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hresult⟩

theorem completeRecordIndex_selected {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView)
    (result : Result × Index) (hresult : completeRecordIndex law view result ≠ 0)
    (selected : FewTimeView) (hselected : view result.1 = some selected) : result.2 = selected.1 := by
  rw [completeRecordIndex_fallback, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨fallback, _, hresult⟩ := hresult
  obtain ⟨source, _, rfl⟩ := map_nonzero_source _ _ _ hresult
  simp only [hselected, Option.elim_some]

theorem completeRecordIndex_effective {Result : Type} (law : SPMF Result) (view : Result → Option FewTimeView)
    (result : Result × Index) (hresult : completeRecordIndex law view result ≠ 0) :
    (view result.1).elim result.2 Prod.fst = result.2 := by
  cases hview : view result.1 with
  | none => rfl
  | some selected =>
      exact (completeRecordIndex_selected law view result hresult selected hview).symm

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazySigning_digestRecord (message : Message) (state : State inputs)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state result ≠ 0) :
    ∃ record loop, result.1 = some record ∧
      loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.memory.external.cache) ∧
      result.2.memory.external.cache = loop.2 ∧
      DigestCompletionPreservesMessages key loop (record.1, result.2.memory.external.cache) := by
  obtain ⟨record, hrecord⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hinputs) state ha hcovered result hresult
  have h := map_nonzero _ eraseSigningTrace (cacheResult result) (map_nonzero _ cacheResult result hresult)
  rw [lazyRun_jointSigningProgram_digestLaw key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key rfl message hinputs state ha hcovered, RetainedObservation.bind_nonzero] at h
  obtain ⟨actual, _, h⟩ := h
  rw [evalDist_map, Functor.map_map] at h
  obtain ⟨loop, hloop, heq⟩ := map_nonzero_source _ _ _ h
  have hvalue : (record.1, result.2.memory.external.cache) = digestCompletionValue state.memory.routing.known words selections actual loop := by
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    simp only [eraseSigningTrace, cacheResult, hrecord, Option.map_some, Prod.map_fst, Prod.map_snd, id_eq] at hfst hsnd
    exact Prod.ext (Option.some.inj hfst) hsnd
  have hcompletion := digestCompletionValue_preservesMessages key state.memory.routing.known words selections actual loop
  rw [← hvalue] at hcompletion
  exact ⟨record, loop, hrecord, (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hloop,
    congrArg Prod.snd hvalue, hcompletion⟩

theorem completedNativeSigning_observed_index (message : Message) (state : State inputs)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : (Option SigningRecord × State inputs) × Index)
    (hresult : completedNativeSigning key inputs hencoding words publicReplies selections rows message state result ≠ 0)
    (record : SigningRecord) (hrecord : result.1.1 = some record) (view : FewTimeView)
    (hview : observedSigningView? (messageAnswers key.parameter result.1.2.memory.external.cache) key.root
      ⟨message, record.1.1⟩ = some view) : result.2 = view.1 := by
  have hraw := map_nonzero _ Prod.fst result hresult
  rw [completedNativeSigning_record] at hraw
  obtain ⟨actualRecord, loop, hr, hloop, _, hcompletion⟩ := lazySigning_digestRecord key inputs hencoding words publicReplies selections rows
    message state hinputs ha hcovered result.1 hraw
  have heq : actualRecord = record := Option.some.inj (hr.symm.trans hrecord)
  subst actualRecord
  cases hs : record.1.1 with
  | none => simp [observedSigningView?, hs] at hview
  | some signature =>
      obtain ⟨output, houtput, _, hselected⟩ := digestCompletion_successful_cached_output key message state.memory.external.cache
        loop hloop (record.1, result.1.2.memory.external.cache) hcompletion signature hs
      dsimp only at houtput hselected
      have hv : hashOutputFewTimeView output = view := by
        simpa [observedSigningView?, hs, messageAnswers, houtput] using hview
      have hselected' : nativeSigningView result.1 = some (hashOutputFewTimeView output) := by
        simp only [nativeSigningView, hrecord, Option.bind_some]
        exact hselected
      exact (completeRecordIndex_selected _ nativeSigningView result hresult _ hselected').trans (congrArg Prod.fst hv)

theorem completedNativeSigning_slots_le (message : Message) (state : State inputs)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter state.memory.external.cache key.root log)
    (result : (Option SigningRecord × State inputs) × Index)
    (hresult : completedNativeSigning key inputs hencoding words publicReplies selections rows message state result ≠ 0)
    (record : SigningRecord) (hrecord : result.1.1 = some record) (index : Index) :
    (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter result.1.2.memory.external.cache)
      key.root (log ++ [⟨message, record.1.1⟩])) index).card ≤
        (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter state.memory.external.cache)
          key.root log) index).card + if result.2 = index then 1 else 0 := by
  have hraw := map_nonzero _ Prod.fst result hresult
  rw [completedNativeSigning_record] at hraw
  obtain ⟨_, loop, _, hloop, hcache, _⟩ := lazySigning_digestRecord key inputs hencoding words publicReplies selections rows
    message state hinputs ha hcovered result.1 hraw
  have hle := simulateQ_romImpl_cache_le _ _ _ hloop
  rw [← hcache] at hle
  have hstable := observedOptionalSigningViews_cache_stable key.parameter key.root _ _ log hle hsigned
  unfold observedOptionalSigningViews
  rw [signingSlotsAtIndex_log_append_card]
  have heq := congrArg (fun views => (signingSlotsAtIndex views index).card) hstable
  apply Nat.add_le_add heq.le
  split_ifs with hobserved hindex hindex
  · exact le_rfl
  · obtain ⟨view, hview, hsource⟩ := hobserved
    exact False.elim (hindex ((completedNativeSigning_observed_index key inputs hencoding words publicReplies selections rows
      message state hinputs ha hcovered result hresult record hrecord view hview).trans hsource))
  · exact Nat.zero_le _
  · exact le_rfl

theorem lazyWorld_observedViews (input : OracleWorld.Domain) (state : State inputs)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter state.memory.external.cache key.root log)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0) :
    observedOptionalSigningViews (messageAnswers key.parameter result.2.memory.external.cache) key.root log =
      observedOptionalSigningViews (messageAnswers key.parameter state.memory.external.cache) key.root log := by
  rw [lazyRun_externalProgram] at hresult
  by_cases hmessage : ∀ hash, input = .inr hash → MessageHashInput key.parameter hash
  · have h := map_nonzero _ cacheResult result hresult
    rw [lazyByteRun_world_message_rom key.parameter inputs hencoding words publicReplies selections rows
      state.memory.routing input hinputs hmessage state hcovered] at h
    obtain ⟨source, hsource, heq⟩ := map_nonzero_source _ _ _ h
    have hcache : result.2.memory.external.cache = source.2 := congrArg Prod.snd heq
    rw [hcache]
    apply observedOptionalSigningViews_cache_stable _ _ _ _ log _ hsigned
    apply simulateQ_romImpl_cache_le (liftM (OracleWorld.query input)) state.memory.external.cache source
    simpa only [simulateQ_spec_query] using (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hsource
  · cases input with
    | inl sample => exact False.elim (hmessage (by intro hash h; cases h))
    | inr input =>
        have hm : ¬MessageHashInput key.parameter input := fun h => hmessage (by intro hash heq; cases heq; exact h)
        have hin : input ∈ inputs := hinputs (by
          simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
        rw [lazyByteRun_hash_nonmessage key.parameter inputs hencoding words publicReplies selections rows
          state.memory.routing input hin state ha hcovered hm result hresult]

end SphincsSecurity.Concrete.RetainedResidual
