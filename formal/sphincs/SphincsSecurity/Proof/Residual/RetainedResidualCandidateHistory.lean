import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualSigningCandidates
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open ResidualByteFrontend (HiddenCandidateBound)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyRun_request_hiddenCandidateBound (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words state.memory.routing.disclosed (project state))
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) :
    HiddenCandidateBound words result.2.memory.routing.disclosed (project result.2) := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      have hafter := lazyByteRun_hiddenCandidateBound key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ hinputs state ha hbound result hresult
      have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ state ha result hresult
      rw [hrouting]
      exact hafter
  | inr message =>
      exact lazyRun_signingProgram_hiddenCandidateBound inputs words publicReplies selections rows key hencoding message hinputs state
        ha hcovered hbound result hresult

end SphincsSecurity.Concrete.RetainedResidual
