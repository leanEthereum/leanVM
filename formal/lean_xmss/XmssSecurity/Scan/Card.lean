module

public import XmssSecurity.Proof.CappedEncodingRejection
public import LeanXmss.Code

@[expose] public section

/-!
# The number of codewords

`validDigests` is in bijection with the digit words of sum `T`, which `LeanXmss.Code` counts.
-/

set_option maxRecDepth 100000

namespace XmssSecurity.TargetSum

/-- A codeword is determined by its digits. -/
theorem validDigests_card_eq :
    validDigests.card = (Finset.univ.filter Valid : Finset Encoding).card := by
  apply Finset.card_bij (fun d _ => digestEncoding d)
  · intro d hd
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hd).2
    have h := decodeDigest_eq_some_iff.mp hx
    have he : digestEncoding d = x := congrArg Prod.fst h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ h.2⟩
  · intro d hd d' hd' he
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hd).2
    obtain ⟨x', hx'⟩ := (Finset.mem_filter.mp hd').2
    have h := (decodeDigest_eq_some_iff.mp hx).1
    have h' := (decodeDigest_eq_some_iff.mp hx').1
    apply digestView_injective
    rw [h, h']
    have he1 : digestEncoding d = x := congrArg Prod.fst h
    have he2 : digestEncoding d' = x' := congrArg Prod.fst h'
    rw [← he1, ← he2, he]
  · intro x hx
    obtain ⟨d, hd⟩ := digestView_surjective (x, 0)
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      x, decodeDigest_eq_some_iff.mpr ⟨hd, (Finset.mem_filter.mp hx).2⟩⟩, congrArg Prod.fst hd⟩

/-- The two libraries' digit words of sum `T` are the same set. -/
theorem card_valid_eq_codeCount :
    (Finset.univ.filter Valid : Finset Encoding).card =
      LeanXmss.Codeword.codeCount LeanXmss.targetSum := by
  have hv : ∀ x : Encoding, Valid x ↔ LeanXmss.Codeword.sum x = LeanXmss.targetSum := fun _ => Iff.rfl
  unfold LeanXmss.Codeword.codeCount
  exact Finset.card_bij (fun x _ => x)
    (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hv x).mp (Finset.mem_filter.mp hx).2⟩)
    (fun _ _ _ _ h => h)
    (fun x hx =>
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hv x).mpr (Finset.mem_filter.mp hx).2⟩, rfl⟩)

theorem validDigests_card :
    validDigests.card = 323504418562481994618807509487594 := by
  rw [validDigests_card_eq, card_valid_eq_codeCount, LeanXmss.Codeword.codeCount_target]

theorem two_pow_107_le_validDigests_card : 2 ^ 107 ≤ validDigests.card := by
  rw [validDigests_card]; norm_num

theorem validDigests_card_le_two_pow_108 : validDigests.card ≤ 2 ^ 108 := by
  rw [validDigests_card]; norm_num

end XmssSecurity.TargetSum
