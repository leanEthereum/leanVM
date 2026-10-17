import XmssSecurity.Proof.CausalAuthenticationPathIndependence
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.MerkleQueryPresence
import XmssSecurity.Proof.CausalKeygenCoupling
import VCVio.ProgramLogic.Relational.Basic

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

def HashCachesAgreeOn (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ input, inputs input → left input = right input

theorem HashCachesAgreeOn.cacheQuery
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (input : HashInput) (output : HashOutput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate hcandidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hagrees candidate hcandidate

theorem HashCachesAgreeOn.cacheQuery_distinct
    (inputs : HashInput → Prop)
    (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn inputs left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ candidate, inputs candidate → candidate ≠ leftInput)
    (hright : ∀ candidate, inputs candidate → candidate ≠ rightInput) :
    HashCachesAgreeOn inputs
      (left.cacheQuery leftInput output)
      (right.cacheQuery rightInput output) := by
  intro candidate hcandidate
  rw [QueryCache.cacheQuery_of_ne left output (hleft candidate hcandidate),
    QueryCache.cacheQuery_of_ne right output (hright candidate hcandidate)]
  exact hagrees candidate hcandidate

theorem relTriple_strengthen_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    {leftProperty : alpha → Prop} {rightProperty : beta → Prop}
    (hrel : RelTriple left right relation)
    (hleft : ∀ result ∈ support left, leftProperty result)
    (hright : ∀ result ∈ support right, rightProperty result) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftProperty leftResult ∧ rightProperty rightResult) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at hrel ⊢
  obtain ⟨coupling, hcoupling⟩ := hrel
  refine ⟨coupling, ?_⟩
  intro pair hpair
  have hleftSupportDist : pair.1 ∈ support 𝒟[left] := by
    rw [← coupling.2.map_fst, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hrightSupportDist : pair.2 ∈ support 𝒟[right] := by
    rw [← coupling.2.map_snd, support_map]
    exact ⟨pair, hpair, rfl⟩
  have hleftSupport : pair.1 ∈ support left := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hleftSupportDist ⊢
    simpa using hleftSupportDist
  have hrightSupport : pair.2 ∈ support right := by
    rw [mem_support_iff_evalDist_apply_ne_zero] at hrightSupportDist ⊢
    simpa using hrightSupportDist
  exact ⟨hcoupling pair hpair,
    hleft pair.1 hleftSupport, hright pair.2 hrightSupport⟩

theorem relTriple_with_support
    {alpha beta : Type}
    {left : ProbComp alpha} {right : ProbComp beta}
    {relation : alpha → beta → Prop}
    (hrel : RelTriple left right relation) :
    RelTriple left right (fun leftResult rightResult =>
      relation leftResult rightResult ∧
        leftResult ∈ support left ∧ rightResult ∈ support right) :=
  relTriple_strengthen_support hrel
    (fun _ hresult => hresult) (fun _ hresult => hresult)

end XmssSecurity
