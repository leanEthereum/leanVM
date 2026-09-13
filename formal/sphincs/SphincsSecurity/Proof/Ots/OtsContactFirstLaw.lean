import SphincsSecurity.Proof.Ots.OtsContactEvents
import SphincsSecurity.Proof.Ots.OtsPrefixContactProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition OtsContactTrace.contacts

def ContactResult.Contacted (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) : Prop :=
  address ∈ OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)

namespace OtsPrefix

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem instrumentedContact_seen (result : Digest × ContactResult × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support) :
    OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) ↔ Contact result.2.2 result.1 := by
  rw [← segment.contactCheckpointRun_project inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    PMF.mem_support_map_iff] at hresult
  obtain ⟨checkpoint, hcheckpoint, rfl⟩ := hresult
  exact (segment.traceCheckpointRun_observation OtsContactTrace.Stopped inputs hencoding hgraph auxiliary secrets ftsSecret words adversary checkpoint hcheckpoint).2.1

theorem instrumentedContact_forget (endpoint : Digest) :
    ContactResult.output <$> segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary =
      segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [instrumentedSeedGame, ← simulateQ_map, contactObserver_forget]
  rw [CausalFrontierProgram.prefix_game]
  rfl

theorem instrumentedContact_real_forget :
    (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).map (fun result => (result.1, result.2.1.output, result.2.2)) =
    realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none) := by
  simpa only [segment.instrumentedContact_forget inputs hencoding hgraph auxiliary secrets ftsSecret words adversary] using
    (realRun_map (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ => ContactResult.output) (fun _ _ => none)).symm

end OtsPrefix

theorem contactSeed_contacted_eq (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (auxiliary : (OtsPrefix.atAddress parameter words address).ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (adversary : Adversary) :
    let segment := OtsPrefix.atAddress parameter words address
    (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).map (fun result => decide (result.2.1.Contacted parameter words address)) =
    (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).map (fun result => decide (Contact result.2.2 result.1)) := by
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
  have hc := segment.instrumentedContact_seen inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
  change result.2.1.frontier address.1 address.2.1 address.2.2.1 address.2.2.2 = result.1 at he
  simp only [ContactResult.Contacted, OtsContactTrace.mem_contacts, he, Function.comp_def]
  rw [hc]
  by_cases hv : value = decide (Contact result.2.2 result.1)
  · simp only [if_pos hv, segment]
  · simp only [if_neg hv]

end SphincsSecurity.Concrete
