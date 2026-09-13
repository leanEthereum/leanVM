import SphincsSecurity.Proof.Ots.OtsTraceRowSource
import SphincsSecurity.Proof.Ots.OtsTwoEdgeTrace
import SphincsSecurity.Proof.Ots.OtsPrefixTwoEdgeProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

def ContactResult.TwoEdgeAt (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) : Prop :=
  OtsContactTrace.SeenTwoEdge (OtsPrefix.atAddress parameter words address)
    (result.frontier address.1 address.2.1 address.2.2.1 address.2.2.2) (result.before * result.after)

theorem OtsPrefix.instrumentedContact_twoEdge (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)
    (result : Digest × ContactResult × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support) :
    OtsContactTrace.SeenTwoEdge segment result.1 (result.2.1.before * result.2.1.after) ↔ TwoEdgeEvent result.2.2 result.1 :=
  (segment.instrumentedContact_rows inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr).twoEdge_iff result.1

theorem contactSeed_twoEdge_eq (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (auxiliary : (OtsPrefix.atAddress parameter words address).ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (adversary : Adversary) :
    let segment := OtsPrefix.atAddress parameter words address
    (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).map (fun result => decide (result.2.1.TwoEdgeAt parameter words address)) =
    (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).map (fun result => decide (TwoEdgeEvent result.2.2 result.1)) := by
  dsimp only
  let segment := OtsPrefix.atAddress parameter words address
  rw [← segment.instrumentedContact_real_forget inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    PMF.map_comp]
  apply PMF.ext
  intro value
  simp only [PMF.map_apply]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support
  swap
  · have hz := not_not.mp hr
    simp only [segment] at hz ⊢
    simp only [hz, ite_self]
  have he := segment.instrumentedContact_endpoint inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
  have hc := segment.instrumentedContact_twoEdge inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
  change result.2.1.frontier address.1 address.2.1 address.2.2.1 address.2.2.2 = result.1 at he
  simp only [ContactResult.TwoEdgeAt, he, Function.comp_def]
  rw [hc]
  by_cases hv : value = decide (TwoEdgeEvent result.2.2 result.1)
  · simp only [if_pos hv, segment]
  · simp only [if_neg hv]

end SphincsSecurity.Concrete
