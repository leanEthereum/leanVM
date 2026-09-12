import SphincsSecurity.Proof.Ots.OtsContactRestart
import SphincsSecurity.Proof.Ots.OtsContactSourceAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsContactTrace.contacts canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

def ContactResult.NewContact (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) : Prop :=
  (result.Marked parameter words ∧ address ∉ OtsContactTrace.contacts parameter words result.frontier result.before) ∧
    address ∈ OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)

theorem ContactResult.newContact_eq_seen (parameter : PublicParameter) (words : OtsReferenceWords)
    (address : OtsPrefix.ChainAddress) (result : ContactResult) (endpoint : Digest)
    (hendpoint : result.frontier address.1 address.2.1 address.2.2.1 address.2.2.2 = endpoint) :
    result.NewContact parameter words address ↔
      (result.Marked parameter words ∧ ¬OtsContactTrace.Seen (OtsPrefix.atAddress parameter words address) endpoint result.before) ∧
      OtsContactTrace.Seen (OtsPrefix.atAddress parameter words address) endpoint (result.before * result.after) := by
  simp only [NewContact, OtsContactTrace.mem_contacts, hendpoint]

theorem OtsPrefix.instrumentedContact_endpoint (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)
    (result : Digest × ContactResult × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support) : result.2.1.frontier segment.lay segment.tree segment.leaf segment.chainIdx = result.1 := by
  rw [← segment.contactCheckpointRun_project inputs hencoding hgraph auxiliary secrets ftsSecret words adversary,
    PMF.mem_support_map_iff] at hresult
  obtain ⟨checkpoint, _, rfl⟩ := hresult
  simp only [OtsPrefix.seedFrontier, OtsPrefix.frontierFromEndpoint, OtsPrefix.replaceChain, OtsPrefix.SameChain,
    and_self, if_true]

variable (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
  (auxiliary : (OtsPrefix.atAddress parameter words address).ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (adversary : Adversary)

theorem contactSeed_newContact_le (budget : Nat)
    (hreal : ∀ result ∈ (realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => (OtsPrefix.atAddress parameter words address).seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support, result.2.1.2.hashCalls ≤ budget)
    (hsmall : budget < Fintype.card Digest) :
    let segment := OtsPrefix.atAddress parameter words address
    let law := realRun (fun _ => OtsPrefix.uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)
    (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
      Pr[fun result => result.2.1.NewContact parameter words address | law]) ≤
      ∑' result, law result * (result.2.1.restartCharge parameter words address : ENNReal) := by
  dsimp only
  let segment := OtsPrefix.atAddress parameter words address
  let law := realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
    (fun _ _ => none)
  have hevent : Pr[fun result => result.2.1.NewContact parameter words address | law] =
      Pr[fun result => (result.2.1.Marked parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before) ∧
        OtsContactTrace.Seen segment result.1 (result.2.1.before * result.2.1.after) | law] := by
    simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
    apply tsum_congr
    intro result
    by_cases hr : result ∈ law.support
    · rw [ContactResult.newContact_eq_seen parameter words address result.2.1 result.1
        (segment.instrumentedContact_endpoint inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr)]
      simp only [segment]
    · have hz : law result = 0 := not_not.mp hr
      simp only [hz, ite_self]
  have hcost : (∑' result, law result * (result.2.1.restartCharge parameter words address : ENNReal)) =
      ∑' result, law result *
        (((OtsContactTrace.prefixCalls segment result.2.1.before + 2 * OtsContactTrace.prefixCalls segment result.2.1.after : Nat) : ENNReal) *
          if result.2.1.Marked parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before then 1 else 0) := by
    apply tsum_congr
    intro result
    by_cases hr : result ∈ law.support
    · have he := segment.instrumentedContact_endpoint inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result hr
      change result.2.1.frontier address.1 address.2.1 address.2.2.1 address.2.2.2 = result.1 at he
      simp only [ContactResult.restartCharge, OtsContactTrace.mem_contacts, he]
      by_cases hm : result.2.1.Marked parameter words ∧ ¬OtsContactTrace.Seen segment result.1 result.2.1.before
      · simp only [segment] at hm ⊢
        simp only [if_pos hm, mul_one]
      · simp only [segment] at hm ⊢
        simp only [if_neg hm, Nat.cast_zero, mul_zero]
    · have hz : law result = 0 := not_not.mp hr
      simp only [hz, zero_mul]
  change (1 - (budget : ENNReal) / Fintype.card Digest) * ((Fintype.card Digest : ENNReal) *
    Pr[fun result => result.2.1.NewContact parameter words address | law]) ≤ _
  rw [hevent]
  rw [show (∑' result, law result * (result.2.1.restartCharge parameter words address : ENNReal)) = _ from hcost]
  exact segment.instrumentedSeed_newContact_le inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget hreal hsmall

end SphincsSecurity.Concrete
