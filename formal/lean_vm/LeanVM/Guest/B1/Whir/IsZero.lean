/-
  LeanVM.Guest.B1.Whir.IsZero

  B1 for `is_zero`: `1` at a zero word, else `0`.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Whir.IsZeroDef
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.B1.Common.Vc

/-!
# `is_zero`

Its body splits the word `w = lo + y·hi` as `split_limbs` does (`split_iff`: the hinted low limb is
the word's) and tests its norm `lo² + x·lo·hi + hi²`, in `K`, against zero: the norm is `0` only at
`w = 0` (`norm_eq_zero_iff`: it is the first limb of `w·w̄`, `w̄ = (lo + x·hi) + y·hi`, and `E` is a
field). `vc` computes its condition; the hint is forced, so the relation is its meaning,
`is_zero_iff`: both its soundness and its completeness.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

private theorem ofK_eq_zero_iff (a : K) : ofK a = 0 ↔ a = 0 := by
  rw [ofK_eq_ofLimbs, zero_eq_ofLimbs, ofLimbs_inj]
  exact and_iff_left rfl

private theorem e_eq_zero_iff (w : E) : w = 0 ↔ w.limb 0 = 0 ∧ w.limb 1 = 0 := by
  conv_lhs => rw [eq_ofLimbs w, zero_eq_ofLimbs, ofLimbs_inj]

/-- **The norm of `a + b·y`**, `a² + x·a·b + b²`, is zero only at `a = b = 0`. -/
theorem norm_eq_zero_iff (a b : K) : a * a + g * a * b + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have key : E.ofLimbs a b * E.ofLimbs (a + g * b) b = E.ofLimbs (a * a + g * a * b + b * b) 0 := by
      rw [mul_limbs, ofLimbs_inj]
      exact ⟨by ring, by linear_combination (a * b + g * (b * b)) * k_two⟩
    rw [h, ← zero_eq_ofLimbs] at key
    rcases mul_eq_zero.mp key with h1 | h1
    · rwa [zero_eq_ofLimbs, ofLimbs_inj] at h1
    · rw [zero_eq_ofLimbs, ofLimbs_inj] at h1
      obtain ⟨h1, rfl⟩ := h1
      exact ⟨by simpa using h1, rfl⟩
  · rintro ⟨rfl, rfl⟩
    ring

/-- The norm, as the body computes it in `E`. -/
private theorem norm_ofK (a b : K) :
    ofK a * ofK a + ofK a * gen * ofK b + ofK b * ofK b = ofK (a * a + g * a * b + b * b) := by
  rw [gen_eq_ofK, ofK_add, ofK_add, ofK_mul, ofK_mul, ofK_mul, ofK_mul]
  ring

/-- **`is_zero`'s core IR is its meaning.** -/
theorem is_zero_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "is_zero" args rets ↔ MeaningIsZero args rets := by
  rw [rel_iff_fnSem (coreProgram_find?_at (j := idx% «is_zero») rfl)]
  rcases args with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> vc [word_y_inv, word_gen] <;> simp only [MeaningIsZero]
  refine ⟨fun ⟨x1, h1, h2, _, h⟩ => ?_, fun h => ⟨ofK (w.limb 0), ?_⟩⟩
  · obtain rfl := (split_iff w x1).mp ⟨h1, h2⟩
    simp only [split_hi, norm_ofK, ofK_eq_zero_iff, norm_eq_zero_iff, ne_eq, word_one, word_zero] at h
    simp only [e_eq_zero_iff]
    by_cases hw : w.limb 0 = 0 ∧ w.limb 1 = 0
    · rw [ite_eq_left hw, ← h.1 hw]
    · rw [ite_eq_right hw, ← h.2 hw]
  · have hs := (split_iff w (ofK (w.limb 0))).mpr rfl
    simp only [split_hi, norm_ofK, ofK_eq_zero_iff, norm_eq_zero_iff, ne_eq, word_one, word_zero] at hs ⊢
    simp only [e_eq_zero_iff] at h
    refine ⟨hs.1, hs.2, ofK_isInK _, fun hz ↦ ?_, fun hz ↦ ?_⟩
    · rw [h, ite_eq_left hz]
    · rw [h, ite_eq_right hz]

end
end LeanVM.Guest.B1
