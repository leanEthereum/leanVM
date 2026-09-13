import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteCandidates
import SphincsSecurity.Proof.Residual.RetainedResidualDigestLaw
import SphincsSecurity.Proof.Residual.RetainedResidualInitial
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem initialState_hiddenCandidateBound (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) :
    HiddenCandidateBound words (fun _ _ _ => False) (project (initialState inputs words exposed)) := by
  intro coordinate hhidden
  change 2 ^ digestBits ≤ (initialAllowed words exposed coordinate).card + 0
  rw [initialAllowed_hidden words exposed coordinate hhidden, Finset.card_univ, Nat.add_zero]
  exact le_of_eq (card_bitVec digestBits).symm

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_hiddenCandidateBound (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs)
    (hbound : HiddenCandidateBound words routing.disclosed (project state)) :
    HiddenCandidateBound words routing.disclosed
      (project (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2) := by
  have h := ResidualByteFrontend.prefixHashQueryResult_hiddenCandidateBound parameter inputs words routing.disclosed
    routing.known hencoding publicReplies selections rows actual seed input (project state) hbound
  rw [← hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state] at h
  exact h

theorem byteRun_hiddenCandidateBound {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (hbound : HiddenCandidateBound words routing.disclosed (project state)) (result : Option Result × State inputs)
    (hresult : byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed computation state result ≠ 0) :
    HiddenCandidateBound words routing.disclosed (project result.2) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [byteRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl input =>
          rw [byteRun_random_bind] at hresult
          obtain ⟨answer, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
          exact ih answer (hnext answer) state hbound result hresult
      | inr input =>
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [byteRun_hash_bind parameter inputs hencoding words publicReplies selections rows routing actual seed input hin] at hresult
          have hafter := checkedHashResult_hiddenCandidateBound parameter inputs hencoding words publicReplies selections rows
            routing actual seed ⟨input, hin⟩ state hbound
          generalize hstep : checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed
            ⟨input, hin⟩ state = step at hresult hafter
          rcases step with ⟨answer, after⟩
          cases answer with
          | none =>
              simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              exact hafter
          | some answer => exact ih answer (hnext answer) after hafter result hresult

theorem lazyByteRun_hiddenCandidateBound {Result : Type} (routing : Routing)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hbound : HiddenCandidateBound words routing.disclosed (project state)) (result : Option Result × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state result ≠ 0) :
    HiddenCandidateBound words routing.disclosed (project result.2) := by
  unfold lazyByteRun at hresult
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact byteRun_hiddenCandidateBound parameter inputs hencoding words publicReplies selections rows routing actual seed
    computation hinputs state hbound result hresult

theorem lazyRun_embed_project {Result : Type} (routing : Routing)
    (computation : OracleComp (ResidualByteFrontend.World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) :
    projectResult <$> lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing) computation) state =
      lazyRun (ResidualByteFrontend.prefixEnvironment parameter inputs hencoding words routing.disclosed routing.known
        publicReplies selections rows) computation (project state) := by
  rw [← run_erasure _ _ state ha, ← run_erasure _ _ (project state) ha]
  simp only [map_bind, observedRun_embed parameter inputs hencoding words publicReplies selections rows routing]
  rfl

end SphincsSecurity.Concrete.RetainedResidual
