import SphincsSecurity.Proof.Residual.RetainedResidualCacheAccounting
import SphincsSecurity.Proof.Residual.RetainedResidualProposalSupport
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyWorld_digestsCached (input : OracleWorld.Domain) (state : State inputs)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter state.memory.external.cache key.root log)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0) :
    SigningDigestsCached key.parameter result.2.memory.external.cache key.root log := by
  rw [lazyRun_externalProgram] at hresult
  by_cases hmessage : ∀ hash, input = .inr hash → MessageHashInput key.parameter hash
  · have h := map_nonzero _ cacheResult result hresult
    rw [lazyByteRun_world_message_rom key.parameter inputs hencoding words publicReplies selections rows
      state.memory.routing input hinputs hmessage state hcovered] at h
    obtain ⟨source, hsource, heq⟩ := map_nonzero_source _ _ _ h
    have hcache : result.2.memory.external.cache = source.2 := congrArg Prod.snd heq
    rw [hcache]
    apply hsigned.mono
    apply simulateQ_romImpl_cache_le (liftM (OracleWorld.query input)) state.memory.external.cache source
    simpa only [simulateQ_spec_query] using (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hsource
  · cases input with
    | inl sample => exact False.elim (hmessage (by intro hash h; cases h))
    | inr input =>
        have hm : ¬MessageHashInput key.parameter input := fun h => hmessage (by intro hash heq; cases heq; exact h)
        have hin : input ∈ inputs := hinputs (by
          simpa only [bind_pure] using mem_hashInputs_hash_bind input pure)
        unfold SigningDigestsCached
        rw [lazyByteRun_hash_nonmessage key.parameter inputs hencoding words publicReplies selections rows
          state.memory.routing input hin state ha hcovered hm result hresult]
        exact hsigned

theorem lazySigning_digestsCached (message : Message) (state : State inputs)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter state.memory.external.cache key.root log)
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧
      SigningDigestsCached key.parameter result.2.memory.external.cache key.root (log ++ [⟨message, record.1.1⟩]) := by
  obtain ⟨record, loop, hrecord, hloop, hcache, hcompletion⟩ :=
    lazySigning_digestRecord key inputs hencoding words publicReplies selections rows message state hinputs ha hcovered result hresult
  have hle := simulateQ_romImpl_cache_le _ _ _ hloop
  rw [← hcache] at hle
  refine ⟨record, hrecord, ?_⟩
  intro entry hentry signature hsignature
  rcases List.mem_append.mp hentry with hold | hnew
  · exact (hsigned.mono hle) entry hold signature hsignature
  · obtain rfl := List.mem_singleton.mp hnew
    obtain ⟨output, houtput, _, _⟩ := digestCompletion_successful_cached_output key message state.memory.external.cache
      loop hloop (record.1, result.2.memory.external.cache) hcompletion signature hsignature
    exact Option.ne_none_iff_exists'.mpr ⟨output, houtput⟩

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_digestsCached (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hsigned : SigningDigestsCached key.parameter state.1.memory.external.cache key.root state.1.memory.log)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    SigningDigestsCached key.parameter result.2.1.memory.external.cache key.root result.2.1.memory.log := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hlog := lazyRun_externalProgram_log key inputs hencoding words publicReplies selections rows _ state.1 hvalid.1 raw hraw
      change SigningDigestsCached key.parameter raw.2.memory.external.cache key.root raw.2.memory.log
      rw [hlog]
      exact lazyWorld_digestsCached key inputs hencoding words publicReplies selections rows input state.1 hinputs hvalid.1 hvalid.2
        state.1.memory.log hsigned raw hraw
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
      obtain ⟨record, hr, hcached⟩ := lazySigning_digestsCached key inputs hencoding words publicReplies selections rows message state.1
        hin hvalid.1 hvalid.2 state.1.memory.log hsigned raw hraw
      have hlog := lazyRun_embed_log key inputs hencoding words publicReplies selections rows _ _ state.1 hvalid.1 raw hraw
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      change SigningDigestsCached key.parameter raw.2.memory.external.cache key.root (raw.2.memory.log ++ [⟨message, record.1.1⟩])
      rwa [hlog]

theorem monitoredRun_query_active {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key (OracleSpec.query input >>= next) ⊆ inputs)
    (hbefore : MonitoredAccounting state) (hbank : MonitoredBankComplete key required state)
    (hsize : CacheSizeBound state.1.memory)
    (hsigned : SigningDigestsCached key.parameter state.1.memory.external.cache key.root state.1.memory.log)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
      (OracleSpec.query input >>= next) state result ≠ 0)
    (hcost : result.2.1.memory.external.hashCalls ≤ budget) (hlog : result.2.1.memory.log.length ≤ signatureLimit)
    (hbudget : budget ≤ 2 ^ 127) (halive : state.2.stopped = false)
    (hclean : ¬ CertificateCacheExceptional key state.1.memory.external.cache) :
    CertificateMonitorActive key budget input (monitorView state) := by
  obtain ⟨hvalidStep, hmacro⟩ := monitoredRun_query_conditions key inputs hencoding words publicReplies selections rows budget required stopAfter
    input next state hvalid hinputs hbefore hbank result hresult hcost hlog halive
  have htotal := ((monitoredRun_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
    (OracleSpec.query input >>= next) state hvalid hinputs hbefore result hresult).2.1).trans hcost
  have hcache := proposalCacheBound_of_no_cache_exception key _ (Finite.of_enncard_le hsize) _ (htotal.trans hbudget) hsize hclean
  rw [← hbefore halive] at hcache htotal
  refine ⟨halive, ⟨?_, hcache, htotal⟩, hvalidStep, hmacro⟩
  change SigningDigestsCached key.parameter state.1.memory.external.cache key.root state.2.log
  rwa [(hbank halive).1]

end SphincsSecurity.Concrete.RetainedResidual
