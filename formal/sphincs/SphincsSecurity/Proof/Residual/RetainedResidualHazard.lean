import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteCheckedHazard
import SphincsSecurity.Proof.Residual.RetainedResidualCandidates
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open ResidualByteFrontend (HiddenCandidateBound probeHazard)
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem prob_checkedHashQuery_stop_le (routing : Routing) (input : inputs) (state : State inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hbound : HiddenCandidateBound words routing.disclosed (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache) :
    Pr[fun result => result.1 = none |
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs routing)
          (ResidualByteFrontend.checkedHashQuery (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state] ≤
      probeHazard state.memory.external.probes := by
  have h := ResidualByteFrontend.prob_checkedPrefixHashQuery_stop_le parameter inputs words routing.disclosed routing.known hencoding
    publicReplies selections rows hselect input (project state) ha hcovered hbound hclean
  rw [← lazyRun_embed_project parameter inputs hencoding words publicReplies selections rows routing _ state ha] at h
  simpa only [probEvent_map, Function.comp_def, projectResult, project] using h

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

end SphincsSecurity.Concrete.RetainedResidual
