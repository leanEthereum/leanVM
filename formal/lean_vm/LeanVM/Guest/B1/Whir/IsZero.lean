/-
  LeanVM.Guest.B1.Whir.IsZero

  B1 for `is_zero`: `1` at a zero word, else `0`.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.B1.Common.Vc

/-!
# `is_zero`

Its body splits the word as `split_limbs` does (`split_iff`: the hinted low limb is the word's)
and tests both limbs against zero. `vc` computes its condition; the hint is forced, so the
relation is its meaning, `is_zero_iff`: both its soundness and its completeness.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`is_zero(w)`**: `1` at `w = 0`, else `0`. -/
def MeaningIsZero : List E → List E → Prop
  | [w], rets => rets = [if w = 0 then 1 else 0]
  | _, _ => False

private theorem ofK_eq_zero_iff (a : K) : ofK a = 0 ↔ a = 0 := by
  rw [ofK_eq_ofLimbs, zero_eq_ofLimbs, ofLimbs_inj]
  exact and_iff_left rfl

private theorem e_eq_zero_iff (w : E) : w = 0 ↔ w.limb 0 = 0 ∧ w.limb 1 = 0 := by
  conv_lhs => rw [eq_ofLimbs w, zero_eq_ofLimbs, ofLimbs_inj]

/-- **`is_zero`'s core IR is its meaning.** -/
theorem is_zero_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "is_zero" args rets ↔ MeaningIsZero args rets := by
  rw [rel_iff_fnSem (coreProgram_find?_at (j := idx% «is_zero») rfl)]
  rcases args with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> vc [word_y_inv] <;> simp only [MeaningIsZero]
  refine ⟨fun ⟨x1, h1, h2, _, h⟩ => ?_, fun h => ⟨ofK (w.limb 0), ?_⟩⟩
  · obtain rfl := (split_iff w x1).mp ⟨h1, h2⟩
    simp only [split_hi, ofK_eq_zero_iff, ne_eq, word_one, word_zero] at h
    simp only [e_eq_zero_iff]
    by_cases ha : w.limb 0 = 0 <;> by_cases hb : w.limb 1 = 0
    · rw [ite_eq_left ⟨ha, hb⟩, ← (h.1 ha).2.1 hb]
    · rw [ite_eq_right (fun h' => hb h'.2), ← (h.1 ha).2.2 hb]
    · rw [ite_eq_right (fun h' => ha h'.1), ← h.2 ha]
    · rw [ite_eq_right (fun h' => ha h'.1), ← h.2 ha]
  · have hs := (split_iff w (ofK (w.limb 0))).mpr rfl
    simp only [split_hi, ofK_eq_zero_iff, ne_eq, word_one, word_zero] at hs ⊢
    simp only [e_eq_zero_iff] at h
    refine ⟨hs.1, hs.2, hs.1, fun ha => ⟨hs.2, fun hb => ?_, fun hb => ?_⟩, fun ha => ?_⟩
    · rw [h, ite_eq_left ⟨ha, hb⟩]
    · rw [h, ite_eq_right (fun h' => hb h'.2)]
    · rw [h, ite_eq_right (fun h' => ha h'.1)]

end
end LeanVM.Guest.B1
