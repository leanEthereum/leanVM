import SphincsSecurity.Proof.Reference.ReferenceContactGame
import SphincsSecurity.Proof.Ots.OtsPrefixInstrumentedSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs OtsContactTrace.contacts

noncomputable abbrev prefixContactObservedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :=
  prefixInstrumentedObservedGame contactObserver inputs hencoding hgraph address dummy adversary

theorem prefixContactObservedGame_original (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixContactObservedGame inputs hencoding hgraph address dummy adversary = referenceContactGame inputs hencoding dummy adversary :=
  prefixInstrumentedObservedGame_original contactObserver inputs hencoding hgraph address dummy adversary

theorem referenceContactGame_restart_allocation (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbound : HasHashQueryBound scheme adversary budget) :
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    (∑ address : OtsPrefix.ChainAddress, ∑' result : InstrumentedResult ContactResult,
      Pr[= result | law] * (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal)) ≤
        ((2 * budget : Nat) : ENNReal) * Pr[fun result => result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) | law] := by
  dsimp only
  let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  calc
    _ = ∑' result : InstrumentedResult ContactResult, Pr[= result | law] *
        ((∑ address : OtsPrefix.ChainAddress, result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : Nat) : ENNReal) := by
      rw [← tsum_fintype (L := SummationFilter.unconditional OtsPrefix.ChainAddress), ENNReal.tsum_comm]
      simp only [tsum_fintype, Nat.cast_sum, Finset.mul_sum, law]
    _ ≤ ∑' result : InstrumentedResult ContactResult, Pr[= result | law] *
        if result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy) then ((2 * budget : Nat) : ENNReal) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support law
      · apply mul_le_mul' le_rfl
        have hcost := (referenceContactGame_cost _ _ dummy adversary result hr).trans
          (referenceContactGame_hashCalls_le dummy adversary budget hbound result hr)
        have hn := ContactResult.restartCharge_sum_le result.1 (referenceFamilyWords result.2.1 dummy) result.2.2 budget hcost
        by_cases hm : result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy)
        · rw [if_pos hm] at hn ⊢
          exact_mod_cast hn
        · rw [if_neg hm] at hn ⊢
          exact_mod_cast hn
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      by_cases hm : result.2.2.Marked result.1 (referenceFamilyWords result.2.1 dummy)
      · simp only [if_pos hm, mul_comm, law]
      · simp only [if_neg hm, mul_zero]

end SphincsSecurity.Concrete
