import SphincsSecurity.Proof.Reference.QueryClassAllocation
import SphincsSecurity.Proof.Ots.OtsPrefixIdealAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem referenceRecordedRest_nonmessage_le (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (referenceRecordedRest key f labels selections dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash key.parameter) result.2 + result.1.2.messageCalls.length ≤
      result.1.2.hashCalls :=
  CausalFrontierProgram.game_nonmessage_recorded_le _ _ _ _ _ _ result (QueryCap.simulate_oracle_mem_support _ _ result hresult)

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

theorem referenceRecordedGame_nonmessage_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy adversary)) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash result.1) result.2.2.2 + result.2.2.1.2.messageCalls.length ≤
      result.2.2.1.2.hashCalls := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  exact referenceRecordedRest_nonmessage_le ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
    (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary output
    (probComp_mem_of_evalDist _ output houtput)

noncomputable def ReferenceRecordedResult.prefixCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  ∑ address : OtsPrefix.ChainAddress,
    QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects result.2.2.2

noncomputable def ReferenceRecordedResult.encodingCalls (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash result.1) result.2.2.2

noncomputable def ReferenceRecordedResult.otherCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  QueryCap.calls (QueryClass.OtherHash result.1 (referenceFamilyWords result.2.1 dummy)) result.2.2.2

def ReferenceRecordedResult.messageCalls (result : ReferenceRecordedResult) : Nat := result.2.2.1.2.messageCalls.length

noncomputable def ReferenceRecordedResult.remainingCalls (dummy : OtsReferenceWords) (result : ReferenceRecordedResult) : Nat :=
  result.encodingCalls + result.otherCalls dummy + result.messageCalls

theorem referenceRecordedGame_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.prefixCalls dummy + result.remainingCalls dummy ≤ q := by
  have hpartition := QueryClass.allocation_calls result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.2
  have hslots := referenceRecordedGame_nonmessage_le _ _ dummy adversary result hresult
  have hbudget := referenceRecordedGame_hashCalls_le dummy adversary q hbound result hresult
  dsimp only [ReferenceRecordedResult.prefixCalls, ReferenceRecordedResult.remainingCalls,
    ReferenceRecordedResult.encodingCalls, ReferenceRecordedResult.otherCalls, ReferenceRecordedResult.messageCalls]
  omega

end SphincsSecurity.Concrete
