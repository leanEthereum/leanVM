import SphincsSecurity.Proof.Ots.OtsTraceRestart
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsContactTrace.contacts canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

def ContactResult.ContactAfterStop (stop : FrontierStop) (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) : Prop :=
  (stop parameter words result.frontier result.before ∧ address ∉ OtsContactTrace.contacts parameter words result.frontier result.before) ∧
    address ∈ OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)

theorem ContactResult.contactAfterStop_eq_seen (stop : FrontierStop) (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) (endpoint : Digest)
    (hendpoint : result.frontier address.1 address.2.1 address.2.2.1 address.2.2.2 = endpoint) :
    result.ContactAfterStop stop parameter words address ↔
      (stop parameter words result.frontier result.before ∧ ¬OtsContactTrace.Seen (OtsPrefix.atAddress parameter words address) endpoint result.before) ∧
      OtsContactTrace.Seen (OtsPrefix.atAddress parameter words address) endpoint (result.before * result.after) := by
  simp only [ContactAfterStop, OtsContactTrace.mem_contacts, hendpoint]

theorem OtsPrefix.instrumentedCheckpoint_endpoint (segment : OtsPrefix) (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)
    (result : Digest × ContactResult × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support) : result.2.1.frontier segment.lay segment.tree segment.leaf segment.chainIdx = result.1 := by
  rw [← segment.traceCheckpointRun_project stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    PMF.mem_support_map_iff] at hresult
  obtain ⟨checkpoint, _, rfl⟩ := hresult
  simp only [OtsPrefix.seedFrontier, OtsPrefix.frontierFromEndpoint, OtsPrefix.replaceChain, OtsPrefix.SameChain,
    and_self, if_true]

theorem checkpointSeed_newContact_le_mark (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)]
    (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (auxiliary : (OtsPrefix.atAddress parameter words address).ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (adversary : Adversary) (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => (OtsPrefix.atAddress parameter words address).seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support, result.2.1.2.hashCalls ≤ budget)
    (hsmall : budget < Fintype.card Digest) :
    let segment := OtsPrefix.atAddress parameter words address
    let law := realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)
    (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
      Pr[fun result => result.2.1.ContactAfterStop stop parameter words address | law]) ≤
      (2 * budget : Nat) * Pr[fun result => stop parameter words result.2.1.frontier result.2.1.before | law] := by
  dsimp only
  let segment := OtsPrefix.atAddress parameter words address
  let law := realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
    (fun _ _ => none)
  have hevent : Pr[fun result => result.2.1.ContactAfterStop stop parameter words address | law] =
      Pr[fun result => (stop parameter words result.2.1.frontier result.2.1.before ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
        OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) | law] := by
    simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
    apply tsum_congr
    intro result
    by_cases hr : result ∈ law.support
    · rw [ContactResult.contactAfterStop_eq_seen stop parameter words address result.2.1 result.1
        (segment.instrumentedCheckpoint_endpoint stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr)]
      simp only [segment]
    · have hz : law result = 0 := not_not.mp hr
      simp only [hz, ite_self]
  change (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
    Pr[fun result => result.2.1.ContactAfterStop stop parameter words address | law]) ≤ _
  rw [hevent]
  exact segment.instrumentedCheckpoint_newContact_le_mark stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall

end SphincsSecurity.Concrete
