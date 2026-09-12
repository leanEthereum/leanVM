import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualSigningLaw
import SphincsSecurity.Proof.Reference.SigningBoundaryHashCost
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
  signDigestLoop publicSignPlan
set_option backward.isDefEq.respectTransparency false

theorem boundaryRun_signDigestLoop_exhaustion (parameter : PublicParameter) (key : SecretKey) (message : Message)
    (attempts : Nat) (cache : QueryCache HashSpec)
    (result : (Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter (signDigestLoop attempts key message) cache))
    (hn : result.1.1 = none) : attempts ≤ result.1.2.hashCalls := by
  induction attempts generalizing cache result with
  | zero => exact Nat.zero_le _
  | succ attempts ih =>
      rw [signDigestLoop, boundaryRun_bind, mem_support_bind_iff] at hr
      obtain ⟨sample, _, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      rw [boundaryRun_bind, mem_support_bind_iff] at hlast
      obtain ⟨attempt, hattempt, hlast⟩ := hlast
      rw [support_map] at hlast
      obtain ⟨tail, htail, rfl⟩ := hlast
      have hcost := boundaryHashAtLeast_signAttempt parameter key message sample.1.1 sample.2 attempt hattempt
      change tail.1.1 = none at hn
      cases hat : attempt.1.1 with
      | none =>
          simp only [hat] at htail
          have h := ih attempt.2 tail htail hn
          simp only [SigningBoundaryTrace.hashCalls_mul]
          omega
      | some selected =>
          simp only [hat, boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at htail
          subst tail
          cases hn

theorem publicSigningWork_hashCalls_min (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (message : Message) (cache : QueryCache HashSpec)
    (result : (PublicSigningRecord × Nat) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl
      (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache)) :
    28504 ≤ result.1.1.2.hashCalls := by
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨loop, hloop, rfl⟩ := hr
  rw [publicDigestLoop_eq, simulateQ_boundaryComputation] at hloop
  change loop ∈ support (boundaryRun key.parameter (signDigestLoop digestAttemptLimit key message) cache) at hloop
  cases hs : loop.1.1 with
  | none =>
      have hc := boundaryRun_signDigestLoop_exhaustion key.parameter key message digestAttemptLimit cache loop hloop hs
      simp only [digestWork, hs]
      exact (show 28504 ≤ digestAttemptLimit by decide).trans hc
  | some selected =>
      simp only [digestWork, hs, SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
      unfold publicSignPlan
      dsimp only
      omega

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram

theorem lazyRun_jointSigningProgram_hashCalls_min (routing : Routing) (message : Message)
    (hinputs : hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ 28504 ≤ record.2.hashCalls := by
  have h := map_nonzero _ cacheResult result hresult
  rw [lazyRun_jointSigningProgram_cache key.parameter inputs hencoding words publicReplies selections rows routing key.root message
    (by simpa only [publicDigestLoop_eq] using hinputs) state ha hcovered, RetainedObservation.bind_nonzero] at h
  obtain ⟨actual, _, h⟩ := h
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at h
  obtain ⟨work, hwork, h⟩ := h
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at h
  refine ⟨_, congrArg Prod.fst h, ?_⟩
  rw [completePublicSigningRecord_trace]
  exact publicSigningWork_hashCalls_min key routing.known words selections message state.memory.external.cache work
    ((mem_support_iff _ _).mpr hwork)

end SphincsSecurity.Concrete.RetainedResidual
